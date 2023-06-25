import type {StoryObj} from '@storybook/react';
import HomePage from "../components/HomePage";

declare const meta: {
    title: string;
    component: typeof HomePage;
    tags: string[];
};
export default meta;
type Story = StoryObj<typeof HomePage>;
export declare const Primary: Story;
